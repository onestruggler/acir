{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D073 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1411 ; wl1417 ; wp1267 ; wl1409 ; wl1412)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K3-at02132031 ; lem-F4-I-K3-at132132 ; lem-F4-I-S2-at02132031 ; lem-F4-I-S2-at132132 ; lem-F4-K3-K3-at02132031 ; lem-F4-K3-K3-at132132 ; lem-F4-S2-I-at02132031 ; lem-F4-S2-I-at132132 ; lem-F4-S2-K3-at02132031 ; lem-F4-S2-K3-at132132 ; lem-F4-S2-S2-at02132031 ; lem-F4-S2-S2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at02132031 ; lem-F4-CS2-CS2-at132132 ; lem-F4-CS2-I-at02132031 ; lem-F4-CS2-I-at132132 ; lem-F4-CS2-S2-at02132031 ; lem-F4-CS2-S2-at132132 ; lem-F4-I-CS2-at02132031 ; lem-F4-I-CS2-at132132 ; lem-F4-S2-CS2-at02132031 ; lem-F4-S2-CS2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at02132031 ; lem-F5-23-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F4-CS2-K3-at02132031 ; lem-F4-CS2-K3-at132132 ; lem-F4-K3-CS2-at02132031 ; lem-F4-K3-CS2-at132132)

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

-- deb-P-lo-split-a @132132: 136 steps
lem-deb-P-lo-split-a-at132132 : Ws → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-P-lo-split-a-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 4 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 3 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 8 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 7 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 6 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 12 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 11 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b1 = at 10 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 9 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 16 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 20 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b2 = at 19 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 18 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 17 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 16 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 24 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 23 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 22 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b3 = at 21 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 20 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 19 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 18 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 28 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 27 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 26 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 25 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b4 = at 24 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 23 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 22 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 21 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 32 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 29 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 26 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 25 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 24 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 36 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 35 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 34 4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-K3-K3-at132132 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b6 = at 33 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 32 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 31 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 30 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 29 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 28 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 27 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 40 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 38 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 37 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 36 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 32 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 44 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b9 = at 38 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 37 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 36 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 35 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 34 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 33 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 48 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 47 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ [])
  b10 = at 46 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 44 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

  b11 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ [])
  b11 = at 38 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 37 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 36 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 52 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 51 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 50 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 49 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 48 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ [])
  b12 = at 47 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 46 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 44 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 43 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 42 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 41 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 40 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ [])
  b13 = at 39 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 56 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 55 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S2-at132132 c4)) ▸
       at 54 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S2-at132132 c4)) ▸
       at 53 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S2-at132132 c4)) ▸
       at 52 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 51 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K3-at132132 c4)) ▸
       at 50 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸ done

  b14 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ [])
  b14 = at 49 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K3-at132132 c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 43 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  b15 = at 60 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 59 4 (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-S2-I-at132132 c4)) ▸
       at 58 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 57 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 56 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 55 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 54 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 53 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  b16 = at 52 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 51 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 50 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 49 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 48 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 47 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 46 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 45 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

-- deb-P-lo-split-b @132132: 66 steps
lem-deb-P-lo-split-b-at132132 : Ws → ⟪ (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-deb-P-lo-split-b-at132132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ [])
  b0 = at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 4 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 3 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 8 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 7 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 6 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 12 1 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl1409 (lit c4)) ▸
       at 11 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ [])
  b1 = at 10 4 (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-K3-K3-at132132 c4)) ▸
       at 9 4 (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K3-CS2-at132132 c4)) ▸
       at 16 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 20 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ S1 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ [])
  b2 = at 19 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 18 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 17 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 16 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 15 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 24 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 23 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 22 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ S1 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ CS12 ∷ CS12 ∷ [])
  b3 = at 21 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 20 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 19 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 18 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 28 1 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl1412 (lit c4)) ▸
       at 27 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 26 4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-S2-S2-at132132 c4)) ▸
       at 25 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS12 ∷ CS12 ∷ [])
  b4 = at 24 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 23 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 22 4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-S2-K3-at132132 c4)) ▸
       at 21 4 (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2-CS2-at132132 c4)) ▸
       at 32 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl1411 (lit c4))) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S2-at132132 c4)) ▸
       at 30 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S2-at132132 c4)) ▸
       at 29 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-I-S2-at132132 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ CS12 ∷ [])
  b5 = at 28 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K3-at132132 c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-I-K3-at132132 c4)) ▸
       at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-I-CS2-at132132 c4)) ▸
       at 36 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at132132 c4)) ▸
       at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S2-at132132 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S2-at132132 c4)) ▸
       at 32 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S2-at132132 c4)) ▸
       at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 29 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 28 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 40 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-23-at132132 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 38 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS2-I-at132132 c4)) ▸
       at 37 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S2-at132132 c4)) ▸
       at 36 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S2-at132132 c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS2-S2-at132132 c4)) ▸
       at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸
       at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 32 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (sym (lem-F4-CS2-K3-at132132 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS2-CS2-at132132 c4)) ▸ done

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
